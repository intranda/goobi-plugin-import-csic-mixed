package de.intranda.goobi.plugins.utils;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.configuration.HierarchicalConfiguration;
import org.apache.commons.configuration.XMLConfiguration;
import org.apache.commons.configuration.tree.xpath.XPathExpressionEngine;
import org.apache.log4j.Logger;

import ugh.exceptions.PreferencesException;

public class DocTypeConfiguration {

    private static final Logger logger = Logger.getLogger(DocTypeConfiguration.class);

    private HierarchicalConfiguration config;
    private List<ConfigItem> docTypeConfigurations = new ArrayList<ConfigItem>();

    public DocTypeConfiguration(XMLConfiguration pluginConfig, String url) {

        String catalogueName = null;
        if (url != null && url.contains(":")) {
            try {
                catalogueName = url.substring(url.lastIndexOf(":"));
                catalogueName = catalogueName.replaceAll("\\W", "");
            } catch (IndexOutOfBoundsException e) {
                logger.error(e);
            }
        }

        pluginConfig.setExpressionEngine(new XPathExpressionEngine());
        if(catalogueName != null) {            
            config = pluginConfig.configurationAt("DocTypeConfig[@catalogue=\"" + catalogueName + "\"]");
        } else {
            config = pluginConfig.configurationAt("DocTypeConfig");
        }
        List<HierarchicalConfiguration> docTypeConfigList = config.configurationsAt("DocType");
        for (HierarchicalConfiguration docTypeConfig : docTypeConfigList) {
            docTypeConfigurations.add(new ConfigItem(docTypeConfig));
        }
    }

    public String getDocType(String typeOfResource, boolean multipart, boolean archive) throws DocTypeConfigurationException {
        ConfigItem selectedItem = null;
        for (ConfigItem item : docTypeConfigurations) {
            if (item.isArchiveMaterial() == archive) {
                if (typeOfResource.equals(item.getTypeOfResource()) || (selectedItem == null && item.getTypeOfResource() == null)) {
                    selectedItem = item;
                }
            }
        }

        if (selectedItem == null) {
            throw new DocTypeConfigurationException("Unable to find matching DocTye configuration for " + typeOfResource);
        }
        if(!multipart && selectedItem.getSingleUnitDocType() != null) {
            return selectedItem.getSingleUnitDocType();
        } else if(selectedItem.getMultipartItemDocType() != null){
            return selectedItem.getMultipartItemDocType();
        } else {
            return selectedItem.getSingleUnitDocType();
        }
    }

    public String getAnchorType(String typeOfResource, boolean multipart, boolean archive) throws DocTypeConfigurationException {
        ConfigItem selectedItem = null;
        for (ConfigItem item : docTypeConfigurations) {
            if (item.isArchiveMaterial() == archive) {
                if (typeOfResource.equals(item.getTypeOfResource()) || (selectedItem == null && item.getTypeOfResource() == null)) {
                    selectedItem = item;
                }
            }
        }
        if (selectedItem == null) {
            throw new DocTypeConfigurationException("Unable to find matching DocTye configuration for " + typeOfResource);
        }
        if(!multipart && selectedItem.getSingleUnitDocType() != null) {
            return null;
        } else if(selectedItem.getMultipartItemDocType() != null){
            return selectedItem.getMultipartAnchorDocType();
        } else{
            return null;
        }
    }

    private static class ConfigItem {
        private String typeOfResource;
        private boolean archiveMaterial;

        private String singleUnitDocType;
        private String multipartItemDocType;
        private String multipartAnchorDocType;

        public ConfigItem(HierarchicalConfiguration docTypeConfig) {
            archiveMaterial = docTypeConfig.getBoolean("@archive", false);
            typeOfResource = docTypeConfig.getString("@typeOfResource");
            singleUnitDocType = docTypeConfig.getString("SingleUnitDocType");
            multipartItemDocType = docTypeConfig.getString("MultipartItemDocType");
            multipartAnchorDocType = docTypeConfig.getString("MultipartAnchorDocType");
        }

        public String getTypeOfResource() {
            return typeOfResource;
        }

        public boolean isArchiveMaterial() {
            return archiveMaterial;
        }

        public String getSingleUnitDocType() {
            return singleUnitDocType;
        }

        public String getMultipartItemDocType() {
            return multipartItemDocType;
        }

        public String getMultipartAnchorDocType() {
            return multipartAnchorDocType;
        }

    }

    public class DocTypeConfigurationException extends PreferencesException {

        public DocTypeConfigurationException() {
            super();
        }

        public DocTypeConfigurationException(String message) {
            super(message);
        }

    }

}
